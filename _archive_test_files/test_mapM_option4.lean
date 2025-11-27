import Lean

theorem List.mapM_mem {α β : Type u_1} (f : α → Option β) (xs : List α) (ys : List β) (y : β)
    (h : xs.mapM f = some ys) (h_mem : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
      simp at h
      rw [h] at h_mem
      simp at h_mem
  | cons a as ih =>
      cases h_fa : f a with
      | none =>
          simp [List.mapM_cons, h_fa] at h
      | some y_head =>
          simp [List.mapM_cons, h_fa] at h
          cases ys with
          | nil =>
              simp at h_mem
          | cons y_head' ys_tail =>
              simp at h_mem
              cases h_mem
              case inl h_eq =>
                  use a, by simp
                  rw [← h_eq]
                  -- h says (mapM f as >>= fun ys' => pure (y_head :: ys')) = some (y_head' :: ys_tail)
                  -- So the first element is y_head, meaning y_head = y_head'
                  sorry
              case inr h_mem_tail =>
                  -- y ∈ ys_tail, need induction
                  sorry
