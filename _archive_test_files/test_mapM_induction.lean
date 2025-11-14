import Lean

theorem List.mapM_mem {α β : Type u_1} (f : α → Option β) (xs : List α) (ys : List β) (y : β)
    (h : xs.mapM f = some ys) (h_mem : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  -- Induction on xs
  induction xs with
  | nil =>
      -- Base case: xs = []
      simp at h
      -- h : ys = []
      rw [h] at h_mem
      -- h_mem : y ∈ []
      simp at h_mem
  | cons a as ih =>
      -- Inductive case: xs = a :: as
      -- mapM (a :: as) f reduces via do-notation
      simp only [List.mapM_cons] at h
      -- h should now be: (match f a with | some val => some val ++ ... | none => none) = some ys
      sorry
